module

public import ConLeche.Kernel.Core
public import ConLeche.Verify.Shift

public section

/-!
# Syntactic facts about the string-literal constructor form

`strLitToConstructor` produces a *closed* expression (constants,
applications and `Nat` literals only): no free variables, no loose
bound variables.  This module exposes the form as a structural
recursion over the character list (`strLitList`) — the induction handle
the walk proofs and the model tier's literal steps share — plus the
closedness facts.
-/

namespace ConLeche

open Expr

/-- The character-list part of `strLitToConstructor`, as a standalone
recursion (the kernel function folds; this is its unfolding). -/
@[expose] def strLitList : List Char → Expr
  | [] => .app (.const listNilName [.zero]) (.const charName [])
  | c :: cs =>
    .app (.app (.app (.const listConsName [.zero]) (.const charName []))
      (.app (.const charOfNatName []) (.lit (.natVal c.toNat))))
      (strLitList cs)

private theorem strLitList_foldr : ∀ cs : List Char,
    cs.foldr
      (fun c e =>
        .app (.app (.app (.const listConsName [.zero]) (.const charName []))
          (.app (.const charOfNatName []) (.lit (.natVal c.toNat)))) e)
      (.app (.const listNilName [.zero]) (.const charName [])) =
    strLitList cs
  | [] => rfl
  | c :: cs => by rw [List.foldr_cons, strLitList_foldr cs, strLitList]

theorem strLitToConstructor_eq (s : String) :
    strLitToConstructor s =
      .app (.const stringOfListName []) (strLitList s.toList) := by
  unfold strLitToConstructor
  rw [strLitList_foldr s.toList]

theorem strLitList_hasFvar : ∀ cs : List Char,
    (strLitList cs).hasFvar = false
  | [] => rfl
  | c :: cs => by
    simp only [strLitList, hasFvar, Bool.or_self, strLitList_hasFvar cs]

/-- The constructor form of a string literal has no free variables. -/
theorem strLitToConstructor_hasFvar (s : String) :
    (strLitToConstructor s).hasFvar = false := by
  rw [strLitToConstructor_eq]
  simp only [hasFvar, strLitList_hasFvar s.toList, Bool.or_self]

theorem strLitList_looseBVarsBounded : ∀ (cs : List Char) (k : Nat),
    (strLitList cs).looseBVarsBounded k = true
  | [], k => rfl
  | c :: cs, k => by
    simp only [strLitList, looseBVarsBounded, Bool.and_self,
      strLitList_looseBVarsBounded cs k]

/-- The constructor form of a string literal has no loose bound
variables. -/
theorem strLitToConstructor_looseBVars (s : String) (k : Nat) :
    (strLitToConstructor s).looseBVarsBounded k = true := by
  rw [strLitToConstructor_eq]
  simp only [looseBVarsBounded, strLitList_looseBVarsBounded s.toList k,
    Bool.and_self]

/-- **THE CONSTRUCTOR FORM RESOLVES WHEREVER THE LITERAL DOES** (task
#315 M8): `constsResolve` at a string literal ASKS for the ten
constants the expansion mentions — the `Nat` trio inside the character
numerals, and `String.mk`, `List.nil`, `List.cons`, `Char`,
`Char.ofNat`, `String` — so the expansion resolves by the literal's own
clause and by nothing else. -/
theorem strLitList_constsResolve {env : Env} (hNat : (env.find? natName).isSome = true)
    (hZ : (env.find? natZeroName).isSome = true)
    (hS : (env.find? natSuccName).isSome = true)
    (hNil : (env.find? listNilName).isSome = true)
    (hCons : (env.find? listConsName).isSome = true)
    (hChar : (env.find? charName).isSome = true)
    (hOfNat : (env.find? charOfNatName).isSome = true) :
    ∀ cs : List Char, (strLitList cs).constsResolve env = true
  | [] => by simp only [strLitList, Expr.constsResolve, Bool.and_eq_true]; exact ⟨hNil, hChar⟩
  | c :: cs => by
    simp only [strLitList, Expr.constsResolve, Bool.and_eq_true]
    refine ⟨⟨⟨hCons, hChar⟩, hOfNat, ?_⟩, strLitList_constsResolve hNat hZ hS hNil
      hCons hChar hOfNat cs⟩
    exact ⟨⟨hNat, hZ⟩, hS⟩

theorem strLitToConstructor_constsResolve {env : Env} {s : String}
    (h : (Expr.lit (.strVal s)).constsResolve env = true) :
    (strLitToConstructor s).constsResolve env = true := by
  simp only [Expr.constsResolve, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hNat, hZ⟩, hS⟩, hStr⟩, hOfList⟩, hList⟩, hNil⟩, hCons⟩, hChar⟩, hOfNat⟩ := h
  rw [strLitToConstructor_eq]
  simp only [Expr.constsResolve, Bool.and_eq_true]
  exact ⟨hOfList, strLitList_constsResolve hNat hZ hS hNil hCons hChar hOfNat s.toList⟩

/-- The constructor form of a string literal is well-scoped at every
depth. -/
theorem strLitToConstructor_WScoped (s : String) (d : Nat) :
    WScoped d (strLitToConstructor s) :=
  WScoped.of_not_hasFvar (strLitToConstructor_hasFvar s)

theorem strLitList_fvarLeaves : ∀ cs : List Char,
    (strLitList cs).fvarLeaves = []
  | [] => by simp only [strLitList, fvarLeaves, List.append_nil]
  | c :: cs => by
    simp only [strLitList, fvarLeaves, List.append_nil,
      strLitList_fvarLeaves cs]

/-- The constructor form of a string literal has no free-variable
leaves. -/
theorem strLitToConstructor_fvarLeaves (s : String) :
    (strLitToConstructor s).fvarLeaves = [] := by
  rw [strLitToConstructor_eq]
  simp only [fvarLeaves, strLitList_fvarLeaves s.toList, List.append_nil]

/-- The constructor form of a string literal is invariant under
depth-shifting (it is closed). -/
theorem strLitToConstructor_shiftFrom (s : String) (p : Nat) :
    shiftFrom p (strLitToConstructor s) = strLitToConstructor s :=
  shiftFrom_eq_self_of_not_hasFvar (strLitToConstructor_hasFvar s)

end ConLeche
