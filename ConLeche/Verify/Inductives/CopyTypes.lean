module

public import ConLeche.Verify.PropRead
public import ConLeche.Verify.PropWhen
public import ConLeche.Verify.EnvWF

public section

/-!
# Annotation commutes with instantiation: the copies' stored types
(task #298)

**What this is for.**  The nested route's elimination mints a copy `A`
of a container member `J` at a pin `J Ds` by *instantiating*: the copy's
type is the container's stored type, level-instantiated and applied to
the pin's components, closed over the block's parameter telescope
(`mkCopy`, `ConLeche/Kernel/Inductives/NestedElim.lean`), and its
constructors the container's the same way (`elimCtors`,
`replaceAllNested`).  The auxiliary block is then installed, which
**re-annotates** those types — and the annotation pass *recomputes*
every binder datum that is not a real input annotation
(`pwWritten pw = !pw.isNever`, `ConLeche/Kernel/Core.lean`), i.e. every
`.never` one, which is every Type-valued binder.  The model lane
(DESIGN §M.21) needs the copies' STORED types to be the container's at
the pin *on the nose, data included*; up to data it has them already.

**The mechanism.**  A recomputed datum is `annotPwPi`'s, and
`annotPwPi` asks the **head-symbol reader** `typeSortPW` first
(`ConLeche/Kernel/PropRead.lean`) and only falls back to inference when
the reader declines.  The reader is a *syntactic* function of the head
symbol, the arity and the binder data — so on the reader's branch the
recomputation commutes with instantiation for elementary reasons, and
this module proves exactly that:

* `SortAgree find? A v` — "`v` reads, for the head reader, like a
  variable declared of type `A`": at every arity, the datum the reader
  computes from `v`'s head is the one it computes from `A`'s telescope.
  This is the hypothesis a *pin component* has to meet, and it is what
  the pin's typing (`pinsOkAux`) says in reader terms.
* `typeSortPW_instantiate1_congr` — the reader cannot tell an opened
  binder from a `SortAgree` value: substituting one for the other
  leaves every reading unchanged.
* `typeSortPW_instantiateLevelParams` — the reader commutes with level
  instantiation through `substPW`, which is the datum's own
  substitution (`Level.zeronessOf_subst`, `Level.substPW_comp`).

Both are one *equation* per reading, with no inference, no reduction and
no environment invariant beyond the stored types' level-parameter
bound (`EnvWF`).

**What is NOT here** — and is the task's honest frontier: the
inference fallback.  Where the reader declines (a `.proj`- or
redex-headed codomain), the datum is `Level.zeronessOf` of an INFERRED
sort, and its stability under instantiation is the general
inference-substitution theorem the tree does not have.  DESIGN's
`#### K.4` states it.
-/

namespace ConLeche

open Expr

/-! ## The spine under instantiation -/

theorem Expr.getAppFn_instantiate1 (v : Expr) :
    ∀ (e : Expr) (d : Nat),
      (e.instantiate1 v d).getAppFn = (e.getAppFn.instantiate1 v d).getAppFn := by
  intro e
  induction e <;> intro d
  case app f a ihf _ => exact ihf d
  all_goals rfl

theorem Expr.numArgs_instantiate1 (v : Expr) :
    ∀ (e : Expr) (d : Nat),
      (e.instantiate1 v d).numArgs
        = (e.getAppFn.instantiate1 v d).numArgs + e.numArgs := by
  intro e
  induction e <;> intro d
  case app f a ihf _ =>
    show (f.instantiate1 v d).numArgs + 1 = _
    rw [ihf d]
    show _ = ((f.getAppFn).instantiate1 v d).numArgs + (f.numArgs + 1)
    omega
  all_goals rfl

theorem Expr.getAppFn_instantiateLevelParams (ks : List Name) (vs : List Level) :
    ∀ (e : Expr),
      (e.instantiateLevelParams ks vs).getAppFn
        = e.getAppFn.instantiateLevelParams ks vs := by
  intro e
  induction e <;> try rfl
  case app f a ihf _ => exact ihf

theorem Expr.numArgs_instantiateLevelParams (ks : List Name) (vs : List Level) :
    ∀ (e : Expr), (e.instantiateLevelParams ks vs).numArgs = e.numArgs := by
  intro e
  induction e <;> try rfl
  case app f a ihf _ => exact congrArg (· + 1) ihf

/-! ## `SortAgree`: a value the head reader cannot tell from a variable -/

/-- **`v` reads like a variable declared of type `A`.**  The
head-symbol reader (`typeSortPW`) answers "what is the zero-ness of the
sort of this type?" from a head symbol and an arity: at an `fvar` head
it peels the DECLARED type's never-data binders and reads the residual
sort (`residualPW (A.peelNeverPis n)`); at a constant head it reads the
stored type the same way and instantiates.  `SortAgree find? A v` says
the two answers coincide at every arity — unapplied (where the reader's
own `∀`/`Sort` cases can fire on `v`, which they never do on a
variable) and at every positive arity.

This is the ONE hypothesis the substitution congruence below needs of
the substituted value, and it is what a pin component's typing says in
the reader's terms: `D : A` gives `typeSortPW find? D = residualPW
(A.peelNeverPis 0)` wherever the reader is complete for `D`. -/
def SortAgree (find? : Name → Option ConstantInfo) (A v : Expr) : Prop :=
  typeSortPW find? v = residualPW (A.peelNeverPis 0) ∧
    ∀ n : Nat, headTypePW find? v.getAppFn (v.numArgs + (n + 1))
      = residualPW (A.peelNeverPis (n + 1))

theorem headTypePW_bvar (find? : Name → Option ConstantInfo) (i n : Nat) :
    headTypePW find? (.bvar i) n = none := rfl

theorem headTypePW_fvar (find? : Name → Option ConstantInfo) (idx n : Nat)
    (A : Expr) :
    headTypePW find? (.fvar idx A) n = residualPW (A.peelNeverPis n) := rfl

/-- The head reader at a positive arity cannot tell the opened binder
from a `SortAgree` value: substituting one for the other leaves every
reading unchanged.  (Positive arity is the *applied* case; the
unapplied one is `typeSortPW_instantiate1_congr`'s `bvar` branch, which
is where `SortAgree`'s first conjunct is spent.) -/
theorem headTypePW_instantiate1_congr (find? : Name → Option ConstantInfo)
    {A v : Expr} (idx : Nat) (h : SortAgree find? A v) :
    ∀ (e : Expr) (d n : Nat),
      headTypePW find? ((e.instantiate1 v d).getAppFn)
          ((e.instantiate1 v d).numArgs + (n + 1))
        = headTypePW find? ((e.instantiate1 (.fvar idx A) d).getAppFn)
          ((e.instantiate1 (.fvar idx A) d).numArgs + (n + 1)) := by
  intro e
  induction e <;> intro d n
  case bvar i =>
    by_cases hi : i = d
    · have hfv : headTypePW find? (Expr.fvar idx A).getAppFn
          ((Expr.fvar idx A).numArgs + (n + 1))
            = residualPW (A.peelNeverPis (n + 1)) := by
        show residualPW (A.peelNeverPis (0 + (n + 1))) = _
        rw [Nat.zero_add]
      show headTypePW find? ((if i = d then v else _).getAppFn)
          ((if i = d then v else _).numArgs + (n + 1))
        = headTypePW find? ((if i = d then (Expr.fvar idx A) else _).getAppFn)
          ((if i = d then (Expr.fvar idx A) else _).numArgs + (n + 1))
      rw [if_pos hi, if_pos hi, hfv]
      exact h.2 n
    · show headTypePW find? ((if i = d then v else _).getAppFn)
          ((if i = d then v else _).numArgs + (n + 1))
        = headTypePW find? ((if i = d then (Expr.fvar idx A) else _).getAppFn)
          ((if i = d then (Expr.fvar idx A) else _).numArgs + (n + 1))
      rw [if_neg hi, if_neg hi]
  case app f a ihf _ =>
    have harg : ∀ m : Nat, m + 1 + (n + 1) = m + (n + 1 + 1) := fun m => by omega
    show headTypePW find? ((f.instantiate1 v d).getAppFn)
        ((f.instantiate1 v d).numArgs + 1 + (n + 1))
      = headTypePW find? ((f.instantiate1 (.fvar idx A) d).getAppFn)
        ((f.instantiate1 (.fvar idx A) d).numArgs + 1 + (n + 1))
    rw [harg, harg]
    exact ihf d (n + 1)
  all_goals rfl

/-- **The reader cannot see a `SortAgree` substitution.**  Every
reading `typeSortPW` makes of a term with the value substituted in is
the reading it makes with the binder opened at a variable of the
declared type — which is what makes the annotation pass's *recomputed*
data agree, node by node, on the two sides. -/
theorem typeSortPW_instantiate1_congr (find? : Name → Option ConstantInfo)
    {A v : Expr} (idx : Nat) (h : SortAgree find? A v) :
    ∀ (e : Expr) (d : Nat),
      typeSortPW find? (e.instantiate1 v d)
        = typeSortPW find? (e.instantiate1 (.fvar idx A) d) := by
  intro e d
  cases e
  case bvar i =>
    by_cases hi : i = d
    · show typeSortPW find? (if i = d then v else _)
        = typeSortPW find? (if i = d then (Expr.fvar idx A) else _)
      rw [if_pos hi, if_pos hi]
      exact h.1
    · show typeSortPW find? (if i = d then v else _)
        = typeSortPW find? (if i = d then (Expr.fvar idx A) else _)
      rw [if_neg hi, if_neg hi]
  case app f a =>
    have hz := headTypePW_instantiate1_congr find? idx h f d 0
    rw [Nat.zero_add] at hz
    show headTypePW find? ((f.instantiate1 v d).getAppFn)
        ((f.instantiate1 v d).numArgs + 1)
      = headTypePW find? ((f.instantiate1 (.fvar idx A) d).getAppFn)
        ((f.instantiate1 (.fvar idx A) d).numArgs + 1)
    exact hz
  all_goals rfl

/-! ## The reader under level instantiation -/

/-- The peeled residual of a type whose level parameters are within
`ps` has its own within `ps`. -/
theorem Expr.allLevelParamsDefined_peelNeverPis {ps : List Name} :
    ∀ (k : Nat) {T R : Expr}, T.peelNeverPis k = some R →
      T.allLevelParamsDefined ps = true → R.allLevelParamsDefined ps = true := by
  intro k
  induction k with
  | zero =>
    intro T R h hT
    rw [← Expr.peelNeverPis_zero_inv h]; exact hT
  | succ k ih =>
    intro T R h hT
    obtain ⟨ty, b, m, rfl, -, hb⟩ := Expr.peelNeverPis_succ_inv h
    rw [Expr.allLevelParamsDefined, Bool.and_eq_true, Bool.and_eq_true] at hT
    exact ih hb hT.1.2

/-- `headTypePW` unfolded at a constant head. -/
theorem headTypePW_const (find? : Name → Option ConstantInfo) (I : Name)
    (us : List Level) (n : Nat) :
    headTypePW find? (.const I us) n =
      match find? I with
      | some ci =>
        if ci.isTowerEntry then none else
        if us.length = ci.toConstantVal.levelParams.length then
          (residualPW (ci.toConstantVal.type.peelNeverPis n)).map
            (Level.substPW ci.toConstantVal.levelParams us)
        else none
      | none => none := rfl

/-- **The head reader commutes with level instantiation**, through the
datum's own substitution `substPW`.  The constant-head case is
`Level.substPW_comp` — the stored type is NOT instantiated, only the
use-site levels are — and the `fvar` case is `Level.zeronessOf_subst`.

The hypothesis is the environment's: every stored type's levels are
within its declared parameters (`ConstWF`, hence `EnvWF`). -/
theorem headTypePW_instantiateLevelParams (find? : Name → Option ConstantInfo)
    {ks : List Name} {vs : List Level}
    (hdef : ∀ n ci, find? n = some ci →
      ci.toConstantVal.type.allLevelParamsDefined ci.toConstantVal.levelParams = true)
    {hd : Expr} {n : Nat} {pw : PropWhen} (h : headTypePW find? hd n = some pw) :
    headTypePW find? (hd.instantiateLevelParams ks vs) n
      = some (Level.substPW ks vs pw) := by
  rcases headTypePW_some_inv find? h with
    ⟨I, us, ci, u, rfl, hf, hnt, hlen, hpeel, rfl⟩ | ⟨idx, ty, u, rfl, hpeel, rfl⟩
  · have hpd : (Level.zeronessOf u).paramsDefined ci.toConstantVal.levelParams = true := by
      refine Level.zeronessOf_paramsDefined ?_
      have := Expr.allLevelParamsDefined_peelNeverPis n hpeel (hdef I ci hf)
      simpa [Expr.allLevelParamsDefined] using this
    show headTypePW find? (.const I (us.map (Level.subst ks vs))) n = _
    rw [headTypePW_const, hf]
    simp only [hnt, Bool.false_eq_true, if_false, List.length_map, hlen, if_true,
      hpeel, residualPW, Option.map_some]
    exact congrArg some
      (Level.substPW_comp (pw := Level.zeronessOf u) hlen hpd).symm
  · show residualPW ((ty.instantiateLevelParams ks vs).peelNeverPis n) = _
    rw [Expr.peelNeverPis_instantiateLevelParams n ks vs hpeel]
    exact congrArg some (Level.zeronessOf_subst ks vs u)

/-- **The reader commutes with level instantiation.**  Every datum the
reader answers with is the instantiated datum of the instantiated
term — a `∀`'s stored datum is `substPW`'d by
`Expr.instantiateLevelParams` itself, a `Sort`'s is `.never` either
way, and a head application's is `headTypePW`'s. -/
theorem typeSortPW_instantiateLevelParams (find? : Name → Option ConstantInfo)
    {ks : List Name} {vs : List Level}
    (hdef : ∀ n ci, find? n = some ci →
      ci.toConstantVal.type.allLevelParamsDefined ci.toConstantVal.levelParams = true)
    {T : Expr} {pw : PropWhen} (h : typeSortPW find? T = some pw) :
    typeSortPW find? (T.instantiateLevelParams ks vs)
      = some (Level.substPW ks vs pw) := by
  cases T
  case forallE ty b m =>
    have : pw = m.pw := (Option.some.inj h).symm
    subst this; rfl
  case sort u =>
    have : pw = .never := (Option.some.inj h).symm
    subst this
    rw [Level.substPW_never]
    rfl
  case const nm us =>
    show headTypePW find? (Expr.const nm (us.map (Level.subst ks vs))) 0 = _
    exact headTypePW_instantiateLevelParams find? hdef (hd := .const nm us) h
  case fvar idx ty =>
    show headTypePW find? (Expr.fvar idx (ty.instantiateLevelParams ks vs)) 0 = _
    exact headTypePW_instantiateLevelParams find? hdef (hd := .fvar idx ty) h
  case app f a =>
    show headTypePW find? ((f.instantiateLevelParams ks vs).getAppFn)
        ((f.instantiateLevelParams ks vs).numArgs + 1) = _
    rw [Expr.getAppFn_instantiateLevelParams, Expr.numArgs_instantiateLevelParams]
    exact headTypePW_instantiateLevelParams find? hdef
      (hd := f.getAppFn) (n := f.numArgs + 1) h
  all_goals exact nomatch h

/-- The reader's environment hypothesis, discharged: every stored
type's level parameters are within its own declared list (`ConstWF`'s
second conjunct). -/
theorem EnvWF.storedLevelParamsDefined {env : Env} (henv : EnvWF env) :
    ∀ n ci, env.find? n = some ci →
      ci.toConstantVal.type.allLevelParamsDefined ci.toConstantVal.levelParams
        = true :=
  fun _ _ h => (henv _ (List.mem_of_find?_eq_some h)).2.1

end ConLeche
