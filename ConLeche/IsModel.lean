module

public import ConLeche.Kernel.Inductives.IotaEq
public import ConLeche.Kernel.Basis
public import ConLeche.SetModel.Ops
public import ConLeche.SetTheory.Derive.Sigma

@[expose] public section

/-!
# What a model of a declaration stream is

This module is the *statement* half of the main theorem: what it means for a set-theoretic
`model` to be a model of the declarations `ds` the checker reads.  It reads the INPUT: every
clause below is about one constant of `ds`, as the stream carries it, and nothing here looks at
the environment the checker builds.  It is written to be read top to bottom in one sitting —
the reading `Expr.eval` of a term as a set, the recursors' rules as propositions read off their
own types (`RuleHolds`), one clause per constant (`ModelOf`), and the definition `IsModel` — and
it imports nothing from the proof tiers.  The main theorems are stated in `ConLeche/Challenge.lean`
(with `sorry`) and proved in `ConLeche/MainTheorem.lean`.

## The model

A model is one function `model : Name → List Nat → V`: the set a constant denotes, given the
values of its universe levels, positionally.  `IsModel V model C` says: every constant of `C`
holds in `model` (`ModelOf model c`), where `C : ConstantInfo → Prop` is a set of constants, as
its membership predicate; of a stream `ds` it is `(· ∈ constantsOf ds)`, every constant of every
declaration (record) of `ds`.  It is pointwise: `ModelOf model c` reads the constant `c` and
nothing else — not even a recursor's constructors, as a recursor's rules are read off its own
type.  So the order of the constants does not matter, a constant listed twice is one, and a name
two constants declare must satisfy both clauses.  The `.olean` input is such a set too: the
constants of the closure's views (`ConLeche/OleanInput.lean`).

## The reading

`Expr.eval model φ ρ e` is the set the checker term `e` denotes, when `φ` assigns a natural to
every universe parameter (`LevelParam`, a name) and `ρ` a set to every de Bruijn index
(`BVarIdx`).  It is a total function with one equation per syntax form (`eval_bvar` … `eval_proj`):

* a constant `c.{us}` denotes `model c` at the values of `us`;
* `Sort u` denotes `univ (Level.eval φ u)`, the types at that level;
* application is the value of a graph at a point (`app`);
* a `∀` denotes the set of dependent function graphs over its domain (`piV`) — or a truth
  value, where its body denotes a truth value on the whole domain; a `λ` denotes the graph of
  its body over its domain (`lamV`) — or the canonical proof `pt`, where its body denotes `pt`
  on the whole domain.  The regime is read off the values, classically, so propositions are
  subsets of a one-element set: proof irrelevance and impredicativity are built into the
  reading, and no typing is consulted;
* a `let` denotes its body at its value;
* a projection `.proj T i e` denotes field `i + 1` of the pair chain `e` denotes (a structure
  value is a right-nested chain whose first component is the constructor's tag);
* a literal denotes what its constructor form (`natLitToConstructor`, `strLitToConstructor`)
  denotes.

Some terms denote junk: a free variable (`fvar`) denotes `∅`, a projection out of something
that is not a structure value denotes whatever that pair chain's component is, and a constant
used at the wrong number of levels reads the first values.  That is harmless: the checker
stores only closed, well-formed terms, and the theorems speak of nothing else.

**Why a total function on the checker's `Expr`.**  The proofs interpret the checker's terms
through their own translation (`interp` over the internal `Term`, `ConLeche/Semantics`), which
is partial and carries the proof's bookkeeping; they show that `Expr.eval` agrees with it
wherever it reads.  A reader of the theorem needs only the equations above.  They are theorems:
the set theory is first-order, so `lamV` and `piV` ask that the body's graph is a set, and the
recursion (`Expr.evalDef`) carries a first-order definition of each value (`DefFun`).

## The set theory

`SetTheory V` (`ConLeche/SetTheory/Core.lean`) is membership `∈ˢ` with extensionality,
pairing, union, power set, regularity, first-order replacement, choice, and an ω-chain of Grothendieck universes.
The reading uses these derived sets (`ConLeche/SetTheory/Derive/*`): `empty`; the pair with its
projections `sfst`/`ssnd`; `app f a`, the value of a graph at a point (`app pt _ = pt`); the
proof point `pt`, the truth values `truthVal p` (`{pt}` if `p`, `∅` otherwise) and
`eqv a b = truthVal (a = b)`; and `univ n`, the types at level `n`: `univ 0` is the set of
truth values.
-/

namespace ConLeche

open SetTheory ConLeche.SetModel

universe w

/-- A universe parameter: a name. -/
abbrev LevelParam := Name

/-- A de Bruijn index: the number of binders between a variable's
occurrence and its binder. -/
abbrev BVarIdx := Nat

variable {V : Type w} [SetTheory V]

/-- Extend a variable environment: the innermost binder gets `x`, every
other index moves up by one. -/
def push (x : V) (ρ : BVarIdx → V) : BVarIdx → V
  | 0 => x
  | i + 1 => ρ i

/-- Component `i` of a right-nested pair chain `⟨x₀, ⟨x₁, ⟨x₂, …⟩⟩⟩`. -/
noncomputable def field : Nat → V → V
  | 0, p => sfst p
  | i + 1, p => field i (ssnd p)

/-- **A declaration's level parameters at values**: the `i`-th parameter gets the `i`-th value
(the first occurrence wins), any other name `0`. -/
def Level.assign : List LevelParam → List Nat → LevelParam → Nat
  | p :: ps, v :: vs, n => if p = n then v else Level.assign ps vs n
  | _, _, _ => 0

/-! ## The reading -/

/-- What the literal `n` denotes: `Nat.zero`, or `Nat.succ` applied to `n - 1`'s. -/
noncomputable def natLitVal (model : Name → List Nat → V) : Nat → V
  | 0 => model natZeroName []
  | n + 1 => app (model natSuccName []) (natLitVal model n)

/-- What a string literal denotes: `String.ofList` of its characters' list, each character
`Char.ofNat` of its code (`strLitToConstructor`). -/
noncomputable def strLitVal (model : Name → List Nat → V) (s : String) : V :=
  app (model stringOfListName []) <|
    s.toList.foldr
      (init := app (model listNilName [0]) (model charName []))
      fun c acc =>
        app (app (app (model listConsName [0]) (model charName []))
          (app (model charOfNatName []) (natLitVal model c.toNat))) acc

/-- `field i` preserves first-order definability. -/
theorem DefFun.field_apply {k : Nat} : ∀ (i : Nat) {P : (Fin k → V) → V},
    DefFun k P → DefFun k fun env => field i (P env)
  | 0, _, hP => DefFun.sfst_apply hP
  | i + 1, _, hP => DefFun.field_apply i (DefFun.ssnd_apply hP)

/-- Prepend a finite `d`-tuple `xs` in front of a de Bruijn environment `ρ`. -/
def prepend {d : Nat} (xs : Fin d → V) (ρ : BVarIdx → V) : BVarIdx → V :=
  fun i => if h : i < d then xs ⟨i, h⟩ else ρ (i - d)

omit [SetTheory V] in
@[simp] theorem prepend_zero (ρ : BVarIdx → V) :
    prepend (Fin.elim0 : Fin 0 → V) ρ = ρ := by
  funext i
  simp [prepend]

omit [SetTheory V] in
theorem prepend_one (xs : Fin 1 → V) (ρ : BVarIdx → V) :
    prepend xs ρ = push (xs 0) ρ := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp [prepend, push]

omit [SetTheory V] in
theorem prepend_fcons {d : Nat} (x : V) (xs : Fin d → V) (ρ : BVarIdx → V) :
    prepend (fcons x xs) ρ = push x (prepend xs ρ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    by_cases h : i < d
    · have h' : i + 1 < d + 1 := Nat.succ_lt_succ h
      simp [prepend, push, h, h', fcons]
    · have h' : ¬ (i + 1 < d + 1) := fun hlt => h (Nat.lt_of_succ_lt_succ hlt)
      simp [prepend, push, h, h']

theorem defFun1_fcons {d : Nat} {F : (Fin (d + 1) → V) → V}
    (hF : DefFun (d + 1) F) (xs : Fin d → V) :
    DefFun 1 fun v => F (fcons (v 0) xs) := by
  let Gs : Fin (d + 1) → (Fin 1 → V) → V
    | ⟨0, _⟩ => fun v => v 0
    | ⟨i + 1, h⟩ => fun _ => xs ⟨i, Nat.lt_of_succ_lt_succ h⟩
  have hGs : ∀ j : Fin (d + 1), DefFun 1 (Gs j) := by
    rintro ⟨j, hj⟩
    cases j with
    | zero => exact DefFun.proj 0
    | succ j => exact DefFun.const (xs ⟨j, Nat.lt_of_succ_lt_succ hj⟩)
  refine (DefFun.comp hF hGs).congr fun v => ?_
  congr 1
  funext ⟨j, hj⟩
  cases j with
  | zero => rfl
  | succ j => rfl

theorem defFun_subst0 {d : Nat} {B : (Fin (d + 1) → V) → V} {A : (Fin d → V) → V}
    (hB : DefFun (d + 1) B) (hA : DefFun d A) :
    DefFun d fun xs => B (fcons (A xs) xs) := by
  let Gs : Fin (d + 1) → (Fin d → V) → V
    | ⟨0, _⟩ => A
    | ⟨i + 1, hi⟩ => fun xs => xs ⟨i, Nat.lt_of_succ_lt_succ hi⟩
  have hGs : ∀ j : Fin (d + 1), DefFun d (Gs j) := by
    rintro ⟨j, hj⟩
    cases j with
    | zero => exact hA
    | succ j => exact DefFun.proj ⟨j, Nat.lt_of_succ_lt_succ hj⟩
  refine (DefFun.comp hB hGs).congr fun xs => ?_
  congr 1
  funext ⟨j, hj⟩
  cases j with
  | zero => rfl
  | succ j => rfl

/-- Proof-carrying worker for `Expr.eval`: evaluates `e` under `d` bound-variable
parameters `xs : Fin d → V` prepended to `ρ`, paired with a `DefFun d` witness. -/
noncomputable def Expr.evalDef (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) : (d : Nat) → Expr → { f : (Fin d → V) → V // DefFun d f }
  | d, .bvar i =>
    if h : i < d then ⟨fun xs => xs ⟨i, h⟩, DefFun.proj ⟨i, h⟩⟩
    else ⟨fun _ => ρ (i - d), DefFun.const _⟩
  | _, .fvar _ _ => ⟨fun _ => empty, DefFun.empty⟩
  | _, .sort u => ⟨fun _ => univ (Level.eval φ u), DefFun.const _⟩
  | _, .const n us => ⟨fun _ => model n (us.map (Level.eval φ)), DefFun.const _⟩
  | d, .app f a =>
    let f' := Expr.evalDef model φ ρ d f
    let a' := Expr.evalDef model φ ρ d a
    ⟨fun xs => SetTheory.app (f'.val xs) (a'.val xs), DefFun.app_apply f'.property a'.property⟩
  | d, .lam ty body =>
    let ty' := Expr.evalDef model φ ρ d ty
    let body' := Expr.evalDef model φ ρ (d + 1) body
    ⟨fun xs => lamV (ty'.val xs) (fun x => body'.val (fcons x xs))
        (hasGraph_of_defFun1 (defFun1_fcons body'.property xs)),
      DefFun.lamV_apply body'.property ty'.property⟩
  | d, .forallE ty body =>
    let ty' := Expr.evalDef model φ ρ d ty
    let body' := Expr.evalDef model φ ρ (d + 1) body
    ⟨fun xs => piV (ty'.val xs) (fun x => body'.val (fcons x xs))
        (hasSigmaPairs_of_defFun1 (defFun1_fcons body'.property xs)),
      DefFun.piV_apply ty'.property body'.property⟩
  | d, .letE _ v body =>
    let v' := Expr.evalDef model φ ρ d v
    let body' := Expr.evalDef model φ ρ (d + 1) body
    ⟨fun xs => body'.val (fcons (v'.val xs) xs), defFun_subst0 body'.property v'.property⟩
  | _, .lit (.natVal n) => ⟨fun _ => natLitVal model n, DefFun.const _⟩
  | _, .lit (.strVal s) => ⟨fun _ => strLitVal model s, DefFun.const _⟩
  | d, .proj _ i e =>
    let e' := Expr.evalDef model φ ρ d e
    ⟨fun xs => field (i + 1) (e'.val xs), DefFun.field_apply (i + 1) e'.property⟩

theorem evalDef_prepend (model : Name → List Nat → V) (φ : LevelParam → Nat) :
    ∀ (e : Expr) (d : Nat) (xs : Fin d → V) (ρ : BVarIdx → V),
      (Expr.evalDef model φ ρ d e).val xs =
        (Expr.evalDef model φ (prepend xs ρ) 0 e).val Fin.elim0
  | .bvar i, d, xs, ρ => by
    by_cases h : i < d
    · simp [Expr.evalDef, prepend, h]
    · simp [Expr.evalDef, prepend, h]
  | .fvar _ _, _, _, _ => rfl
  | .sort _, _, _, _ => rfl
  | .const _ _, _, _, _ => rfl
  | .app f a, d, xs, ρ => by
    simp only [Expr.evalDef]
    rw [evalDef_prepend model φ f d xs ρ, evalDef_prepend model φ a d xs ρ]
  | .lam ty body, d, xs, ρ => by
    simp only [Expr.evalDef]
    refine lamV_ext (evalDef_prepend model φ ty d xs ρ) _ _ fun x _ => ?_
    rw [evalDef_prepend model φ body (d + 1) (fcons x xs) ρ,
        evalDef_prepend model φ body 1 (fcons x Fin.elim0) (prepend xs ρ),
        prepend_fcons, prepend_fcons, prepend_zero]
  | .forallE ty body, d, xs, ρ => by
    simp only [Expr.evalDef]
    refine piV_ext (evalDef_prepend model φ ty d xs ρ) _ _ fun x _ => ?_
    rw [evalDef_prepend model φ body (d + 1) (fcons x xs) ρ,
        evalDef_prepend model φ body 1 (fcons x Fin.elim0) (prepend xs ρ),
        prepend_fcons, prepend_fcons, prepend_zero]
  | .letE _ v body, d, xs, ρ => by
    simp only [Expr.evalDef]
    rw [evalDef_prepend model φ v d xs ρ,
        evalDef_prepend model φ body (d + 1) (fcons _ xs) ρ,
        evalDef_prepend model φ body 1 (fcons _ Fin.elim0) (prepend xs ρ),
        prepend_fcons, prepend_fcons, prepend_zero]
  | .lit (.natVal _), _, _, _ => rfl
  | .lit (.strVal _), _, _, _ => rfl
  | .proj _ i e, d, xs, ρ => by
    simp only [Expr.evalDef]
    rw [evalDef_prepend model φ e d xs ρ]

/-- **The set a term denotes**: see the module docstring. -/
noncomputable def Expr.eval (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (e : Expr) : V :=
  (Expr.evalDef model φ ρ 0 e).val Fin.elim0

theorem eval_defFun_prepend (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (d : Nat) (e : Expr) :
    DefFun d fun xs => Expr.eval model φ (prepend xs ρ) e := by
  refine (Expr.evalDef model φ ρ d e).property.congr fun xs => ?_
  exact evalDef_prepend model φ e d xs ρ

theorem eval_hasGraph_push (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (A : V) (body : Expr) :
    HasGraph A fun x => Expr.eval model φ (push x ρ) body :=
  hasGraph_of_defFun1 <| (eval_defFun_prepend model φ ρ 1 body).congr fun xs => by
    rw [prepend_one]

theorem eval_hasSigmaPairs_push (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (A : V) (body : Expr) :
    HasSigmaPairs A fun x => Expr.eval model φ (push x ρ) body :=
  hasSigmaPairs_of_defFun1 <| (eval_defFun_prepend model φ ρ 1 body).congr fun xs => by
    rw [prepend_one]

@[simp] theorem eval_bvar (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (i : BVarIdx) :
    Expr.eval model φ ρ (.bvar i) = ρ i := by
  simp [Expr.eval, Expr.evalDef]

@[simp] theorem eval_fvar (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (idx : Nat) (ty : Expr) :
    Expr.eval model φ ρ (.fvar idx ty) = empty := rfl

@[simp] theorem eval_sort (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (u : Level) :
    Expr.eval model φ ρ (.sort u) = univ (Level.eval φ u) := rfl

@[simp] theorem eval_const (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (n : Name) (us : List Level) :
    Expr.eval model φ ρ (.const n us) = model n (us.map (Level.eval φ)) := rfl

@[simp] theorem eval_app (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (f a : Expr) :
    Expr.eval model φ ρ (.app f a) =
      SetTheory.app (Expr.eval model φ ρ f) (Expr.eval model φ ρ a) := rfl

@[simp] theorem eval_lam (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (ty body : Expr) :
    Expr.eval model φ ρ (.lam ty body) =
      lamV (Expr.eval model φ ρ ty) (fun x => Expr.eval model φ (push x ρ) body)
        (eval_hasGraph_push model φ ρ (Expr.eval model φ ρ ty) body) := by
  simp only [Expr.eval, Expr.evalDef]
  refine lamV_congr _ _ fun x _ => ?_
  rw [evalDef_prepend model φ body 1 (fcons x Fin.elim0) ρ, prepend_fcons, prepend_zero]

@[simp] theorem eval_forallE (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (ty body : Expr) :
    Expr.eval model φ ρ (.forallE ty body) =
      piV (Expr.eval model φ ρ ty) (fun x => Expr.eval model φ (push x ρ) body)
        (eval_hasSigmaPairs_push model φ ρ (Expr.eval model φ ρ ty) body) := by
  simp only [Expr.eval, Expr.evalDef]
  refine piV_congr _ _ fun x _ => ?_
  rw [evalDef_prepend model φ body 1 (fcons x Fin.elim0) ρ, prepend_fcons, prepend_zero]

@[simp] theorem eval_letE (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (ty v body : Expr) :
    Expr.eval model φ ρ (.letE ty v body) =
      Expr.eval model φ (push (Expr.eval model φ ρ v) ρ) body := by
  simp only [Expr.eval, Expr.evalDef]
  rw [evalDef_prepend model φ body 1 (fcons _ Fin.elim0) ρ, prepend_fcons, prepend_zero]

@[simp] theorem eval_lit_nat (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (n : Nat) :
    Expr.eval model φ ρ (.lit (.natVal n)) = natLitVal model n := rfl

@[simp] theorem eval_lit_str (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (s : String) :
    Expr.eval model φ ρ (.lit (.strVal s)) = strLitVal model s := rfl

@[simp] theorem eval_proj (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (T : Name) (i : Nat) (e : Expr) :
    Expr.eval model φ ρ (.proj T i e) = field (i + 1) (Expr.eval model φ ρ e) := rfl

/-- The variable environment a closed term is read at (it reads none of it). -/
noncomputable def ρ₀ : BVarIdx → V := fun _ => empty

/-- **The constants a declaration (a record of the input) contributes to the model's clauses.**

* An axiom is its statement.  `sorryAx`, the hole, contributes nothing: a hole is read where it
  is used, as the axiom of the statement it fills.
* A definition is its statement and its value — unless the value uses a hole: then it is read
  as an axiom of its statement.
* A theorem and an `opaque` are their statements: the value is never read, so an opaque
  constant stays free.
* An inductive block is its constants: type formers, constructors and recursors, each read on
  its own.
* A quotient constant, and the axiom `Quot.sound`, are the quotient package's constant at the
  record's level-parameter names (`quotAt`): `Quot.lift` and `Quot.ind` carry their ι rule
  there. -/
def Declaration.constants : Declaration → List ConstantInfo
  | .axiomDecl cv =>
    if cv.name = quotSoundName then [quotAt .sound cv]
    else if cv.name = sorryAxName then []
    else [.axiomInfo cv]
  | .defnDecl cv v hint => if usesSorry v then [.axiomInfo cv] else [.defnInfo cv v hint]
  | .thmDecl cv _ => [.thmInfo cv]
  | .opaqueDecl cv _ => [.axiomInfo cv]
  | .quotDecl k cv => [quotAt k cv]
  | .indDecl block _ => block

/-! ## The clauses -/

/-- **The constants of the declarations `ds`**: every constant of every one of them, in order. -/
def constantsOf (ds : List Declaration) : List ConstantInfo := ds.flatMap Declaration.constants

/-- **A recursor's rule `i` holds** at the level assignment `φ`: its ι equation, read off the
recursor's own type (`iotaEqOf`, `ConLeche/Kernel/Inductives/IotaEq.lean`), denotes an
inhabited set (a true proposition).  The rule `i` reads the `i`-th minor premise of the motive the
recursor's type applies:

    ∀ (prefix) (fields), @Eq.{u} (motive idx (C.{us} params fields))
      (rec prefix idx (C.{us} params fields)) (rhs prefix fields)

where `prefix` are the recursor's first `rP` binders, `fields` the minor premise's first
`nfields` binders (its induction hypotheses are not quantified), `idx` its conclusion's index
arguments, `C` the rule's constructor at the levels `us` and the parameters `params` of the major
premise's type, `rhs` the rule's right-hand side and `u` the motive's sort level.  Nothing else
is read: no constructor constant, no firing mode. -/
def RuleHolds (V : Type w) [SetTheory V] (model : Name → List Nat → V)
    (φ : LevelParam → Nat) (cv : ConstantVal) (mI rP i : Nat) (rl : RecRule) : Prop :=
  ∀ e, iotaEqOf cv mI rP i rl = some e → ∃ x, x ∈ˢ Expr.eval model φ ρ₀ e

/-- **The constant `c` holds in `model`**: at every list of level values `vals`, one per level
parameter, read through `φ := Level.assign ps vals`,

* the constant is a member of what its type denotes;
* a definition is what its value denotes;
* every rule of a recursor holds (`RuleHolds`), by its position.

It reads `c` alone. -/
def ModelOf {V : Type w} [SetTheory V] (model : Name → List Nat → V) (c : ConstantInfo) : Prop :=
  ∀ vals : List Nat, vals.length = c.toConstantVal.levelParams.length →
    let φ := Level.assign c.toConstantVal.levelParams vals
    model c.name vals ∈ˢ Expr.eval model φ ρ₀ c.toConstantVal.type ∧
    match c with
    | .defnInfo _ value _ => model c.name vals = Expr.eval model φ ρ₀ value
    | .recInfo cv mI rP _ rules => ∀ i rl, rules[i]? = some rl → RuleHolds V model φ cv mI rP i rl
    | _ => True

/-- **`model` is a model of the constants `C`**: every one of them holds, each on its own
(`ModelOf`).  Of a declaration stream `ds`, it is a model of `(· ∈ constantsOf ds)`. -/
def IsModel (V : Type w) [SetTheory V] (model : Name → List Nat → V)
    (C : ConstantInfo → Prop) : Prop :=
  ∀ c, C c → ModelOf model c

/-! ## The prelude's `False` and `Eq`

Nothing above treats `False` or `Eq` specially: `False` is whatever `model` makes it, and so is
`Eq`.  What makes them mean the empty proposition and equality is their declarations, through
their own clauses: `False.rec`'s membership forces `⟦False⟧ = ∅`, and `Eq.refl` with `Eq.rec`
force `⟦@Eq A a b⟧ = eqv a b` (`IsModel.false_empty`, `IsModel.eq_eqv`,
`ConLeche/Semantics/IsModelBasis.lean`).  These are the constants the prelude declares them
with, as a stream carries them (at any level-parameter names); the checker accepts a stream
declaring `False` or `Eq` only with them. -/

/-- A constant's type. -/
abbrev ConstantInfo.type (c : ConstantInfo) : Expr := c.toConstantVal.type

/-- `C` has a constant named `n`. -/
def DeclaresName (C : ConstantInfo → Prop) (n : Name) : Prop :=
  ∃ c, C c ∧ c.name = n

/-- `C` has a constant `n` at the level parameters `ps` with the type `T`. -/
def HasConstant (C : ConstantInfo → Prop) (n : Name) (ps : List LevelParam) (T : Expr) : Prop :=
  ∃ c, C c ∧ c.toConstantVal = ⟨n, ps, T⟩

/-- `False.rec.{u} : (motive : False → Sort u) → (t : False) → motive t`. -/
def falseRecType (u : Level) : Expr :=
  .forallE (.forallE (.const falseName []) (.sort u)) <|
    .forallE (.const falseName []) (.app (.bvar 1) (.bvar 0))

/-- `Eq.{u} : {α : Sort u} → α → α → Prop`. -/
def eqType (u : Level) : Expr :=
  .forallE (.sort u) <| .forallE (.bvar 0) <| .forallE (.bvar 1) (.sort .zero)

/-- `@Eq.{u} α a b`, under binders where `α`, `a`, `b` are the given terms. -/
def eqApp (u : Level) (α a b : Expr) : Expr :=
  .app (.app (.app (.const eqName [u]) α) a) b

/-- `Eq.refl.{u} : ∀ {α : Sort u} (a : α), @Eq α a a`. -/
def eqReflType (u : Level) : Expr :=
  .forallE (.sort u) <| .forallE (.bvar 0) (eqApp u (.bvar 1) (.bvar 0) (.bvar 0))

/-- `Eq.rec.{u_1, u} : ∀ {α : Sort u} {a : α} {motive : (b : α) → a = b → Sort u_1},
motive a (Eq.refl a) → ∀ {b : α} (t : a = b), motive b t`. -/
def eqRecType (u₁ u : Level) : Expr :=
  .forallE (.sort u) <|
  .forallE (.bvar 0) <|
  .forallE (.forallE (.bvar 1) (.forallE (eqApp u (.bvar 2) (.bvar 1) (.bvar 0)) (.sort u₁))) <|
  .forallE (.app (.app (.bvar 0) (.bvar 1))
    (.app (.app (.const eqReflName [u]) (.bvar 2)) (.bvar 1))) <|
  .forallE (.bvar 3) <|
  .forallE (eqApp u (.bvar 4) (.bvar 3) (.bvar 0)) <|
  .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)

/-- **`C` declares the prelude's `False`**: its eliminator, at some level-parameter name. -/
def DeclaresFalse (C : ConstantInfo → Prop) : Prop :=
  ∃ p, HasConstant C (falseName.str "rec") [p] (falseRecType (.param p))

/-- **`C` declares the prelude's `Eq`**: the type former, `Eq.refl` and `Eq.rec`, each at
some (distinct) level-parameter names. -/
def DeclaresEq (C : ConstantInfo → Prop) : Prop :=
  (∃ p, HasConstant C eqName [p] (eqType (.param p))) ∧
  (∃ p, HasConstant C eqReflName [p] (eqReflType (.param p))) ∧
  (∃ p₁ p, p₁ ≠ p ∧ HasConstant C (eqName.str "rec") [p₁, p] (eqRecType (.param p₁) (.param p)))

end ConLeche
