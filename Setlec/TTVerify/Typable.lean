import Setlec.TTVerify.Inversion

/-!
# `Typable`, and inversion for it

`Typable Γ e` — "`e` has *some* type in `Γ`" — together with the family
of lemmas that push it into subterms.

It is what a **precondition** on a bridge claim would be phrased with:
`infer` establishes typing and so takes no precondition, while `whnf`
and `isDefEq` may assume their input well-typed, and pushing such an
assumption through a recursive call needs exactly "the subterms of a
typable term are typable".

**Why this is cheap, and what bounds it.**  It is inversion *up to
`conv`*, and `conv` does not change the subject, so the subject of a
derivation determines which rule could have concluded it.  Each member
is one induction with one interesting case, the `conv` case (which
recurses on the same subject), and a catch-all closed by constructor
disjointness.  Nothing here resembles Church–Rosser, unique typing, or
weakening — and in particular **it is strictly weaker than inversion on
derivations**: it recovers *a* typing for each subterm, not the
premises of the last rule at the ambient type.

## Three gaps, all structural

The family is not "one lemma per former", and the exceptions say
something about the layer rather than about this module.

* **`lam` gives the body, not the domain.**  `HasType.lam`'s only
  premise is the body's typing (`Setlec/TT/Judgment.lean`), so a
  typable `λ` tells you nothing about its annotation.  That is the
  layer's own "rules carry exactly the premises soundness consumes"
  discipline, seen from the consumer side.
* **`eqE` gives nothing.**  `eqType` is premise-free: *every*
  `.eqE T a b` is typable, at `Sort 0`, whatever `T`, `a` and `b` are.
  This is the same fact as `VExpr`'s "`ty` is never checked".
* **`letE` gives the *substituted* body**, not the body under a binder
  — matching `HasType.letE`, which types `body.inst val`.  A consumer
  wanting the open body will not find it here, and should not: the
  layer never types it (recorded finding: opening a `let` body with an
  opaque variable is provably too weak for real streams).
-/

namespace Setlec.TTVerify

open Setlec.TT

/-- `e` has some type in `Γ`. -/
def Typable (Γ : List VExpr) (e : VExpr) : Prop := ∃ T, HasType Γ e T

theorem Typable.intro {Γ : List VExpr} {e T : VExpr} (h : HasType Γ e T) :
    Typable Γ e := ⟨T, h⟩

/-! ## The family -/

/-- A typable application has a typable head. -/
theorem Typable.appFn {Γ : List VExpr} {f a : VExpr}
    (h : Typable Γ (.app f a)) : Typable Γ f :=
  (hasType_appFn h.choose_spec).elim fun _ h => h.elim fun _ h => ⟨_, h⟩

/-- …and a typable argument. -/
theorem Typable.appArg {Γ : List VExpr} {f a : VExpr}
    (h : Typable Γ (.app f a)) : Typable Γ a :=
  (hasType_appArg h.choose_spec).elim fun _ h => ⟨_, h⟩

/-- A typable projection has a typable subject. -/
theorem Typable.projSubj {Γ : List VExpr} {i : Nat} {p : VExpr}
    (h : Typable Γ (.proj i p)) : Typable Γ p :=
  (hasType_projSubj h.choose_spec).elim fun _ h => ⟨_, h⟩

/-- Inversion for `λ`: the body is typable **in the extended
context**.  The domain is not recoverable — see the module header. -/
theorem hasType_lam_inv :
    ∀ {Δ : List VExpr} {e C : VExpr}, HasType Δ e C →
      ∀ {A b : VExpr}, e = .lam A b → Typable (A :: Δ) b := by
  intro Δ e C h
  induction h with
  | lam hb =>
    intro A b he
    simp only [VExpr.lam.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨_, hb⟩
  | conv _ _ ih _ => intro A b he; exact ih he
  | _ => intro A b he; cases he

/-- A typable `λ` has a typable body, one binder deeper. -/
theorem Typable.lamBody {Γ : List VExpr} {A b : VExpr}
    (h : Typable Γ (.lam A b)) : Typable (A :: Γ) b :=
  hasType_lam_inv h.choose_spec rfl

/-- Inversion for `Π`: both the domain and the codomain are typed, at
sorts.  The one member that returns the *premises* rather than merely
typability, because `pi` is the one former whose premises are already
in that shape. -/
theorem hasType_pi_inv :
    ∀ {Δ : List VExpr} {e C : VExpr}, HasType Δ e C →
      ∀ {A B : VExpr}, e = .pi A B →
        ∃ u v, HasType Δ A (.sort u) ∧ HasType (A :: Δ) B (.sort v) := by
  intro Δ e C h
  induction h with
  | pi hA hB =>
    intro A B he
    simp only [VExpr.pi.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨_, _, hA, hB⟩
  | conv _ _ ih _ => intro A B he; exact ih he
  | _ => intro A B he; cases he

/-- A typable `Π` has a typable domain. -/
theorem Typable.piDom {Γ : List VExpr} {A B : VExpr}
    (h : Typable Γ (.pi A B)) : Typable Γ A :=
  (hasType_pi_inv h.choose_spec rfl).elim fun _ h =>
    h.elim fun _ h => ⟨_, h.1⟩

/-- …and a typable codomain, one binder deeper. -/
theorem Typable.piCod {Γ : List VExpr} {A B : VExpr}
    (h : Typable Γ (.pi A B)) : Typable (A :: Γ) B :=
  (hasType_pi_inv h.choose_spec rfl).elim fun _ h =>
    h.elim fun _ h => ⟨_, h.2⟩

/-- Inversion for `let`: the annotation and the value are typed, and
the body is typed **already substituted**. -/
theorem hasType_letE_inv :
    ∀ {Δ : List VExpr} {e C : VExpr}, HasType Δ e C →
      ∀ {ty val body : VExpr}, e = .letE ty val body →
        (∃ u, HasType Δ ty (.sort u)) ∧ HasType Δ val ty ∧
          Typable Δ (body.inst val) := by
  intro Δ e C h
  induction h with
  | letE hty hval hbody =>
    intro ty val body he
    simp only [VExpr.letE.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨⟨_, hty⟩, hval, ⟨_, hbody⟩⟩
  | conv _ _ ih _ => intro ty val body he; exact ih he
  | _ => intro ty val body he; cases he

/-- A typable `let` has a typable value. -/
theorem Typable.letVal {Γ : List VExpr} {ty val body : VExpr}
    (h : Typable Γ (.letE ty val body)) : Typable Γ val :=
  ⟨ty, (hasType_letE_inv h.choose_spec rfl).2.1⟩

/-- …and a typable zeta reduct.  Note this is the *substituted* body:
the layer never types the open one. -/
theorem Typable.letBody {Γ : List VExpr} {ty val body : VExpr}
    (h : Typable Γ (.letE ty val body)) : Typable Γ (body.inst val) :=
  (hasType_letE_inv h.choose_spec rfl).2.2

/-! ## The leaves

Typability is trivially closed under `conv`, because `Typable` forgets
the type — that is why each member above costs one `conv` case rather
than a confluence argument, and it needs no lemma of its own
(`Typable.intro` is already it).

An earlier draft *did* state it as a lemma taking the `Deq` and
ignoring it.  That is §8.2's over-strong shape in the increment that
records §8.2, so it is prose here instead. -/

/-- Every leaf is typable outright, with no hypothesis: sorts,
constants and equations.  (`bvar` is the exception — it needs its index
in range, which is a fact about `Γ`, not about the term.) -/
theorem Typable.sort {Γ : List VExpr} (u : Nat) :
    Typable Γ (.sort u) := ⟨_, .sort⟩

theorem Typable.const {Γ : List VExpr} (c : BConst) (us : List Nat) :
    Typable Γ (.const c us) := ⟨_, .const⟩

theorem Typable.eqE {Γ : List VExpr} (T a b : VExpr) :
    Typable Γ (.eqE T a b) := ⟨_, .eqType⟩

end Setlec.TTVerify
